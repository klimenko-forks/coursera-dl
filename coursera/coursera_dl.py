#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Authors and copyright:
#     © 2012-2013, John Lehmann (first last at geemail dotcom or @jplehmann)
#     © 2012-2015, Rogério Brito (r lastname at ime usp br)
#     © 2013, Jonas De Taeye (first dt at fastmail fm)
#
# Contributions are welcome, but please add new unit tests to test your changes
# and/or features.  Also, please try to make changes platform independent and
# backward compatible.
#
# Legalese:
#
#  This program is free software: you can redistribute it and/or modify it
#  under the terms of the GNU Lesser General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or (at your
#  option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.


"""
Module for downloading lecture resources such as videos for Coursera classes.

Given a class name, username and password, it scrapes the course listing
page to get the section (week) and lecture names, and then downloads the
related materials into appropriately named files and directories.

Examples:
  coursera-dl -u <user> -p <passwd> saas
  coursera-dl -u <user> -p <passwd> -l listing.html -o saas --skip-download

For further documentation and examples, visit the project's home at:
  https://github.com/coursera-dl/coursera
"""

import argparse
import datetime
import glob
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import time

from distutils.version import LooseVersion as V

import requests

from six import iteritems

from .cookies import (
    AuthenticationFailed, ClassNotFound,
    get_cookies_for_class, make_cookie_values, login, TLSAdapter)
from .credentials import get_credentials, CredentialsError, keyring
from .define import (CLASS_URL, ABOUT_URL, PATH_CACHE,
                     OPENCOURSE_CONTENT_URL, OPENCOURSE_VIDEO_URL)
from .downloaders import get_downloader
from .utils import (clean_filename, get_anchor_format, mkdir_p, fix_url,
                    decode_input, make_coursera_absolute_url)

# URL containing information about outdated modules
_SEE_URL = " See https://github.com/coursera-dl/coursera/issues/139"

# Test versions of some critical modules.
# We may, perhaps, want to move these elsewhere.
import bs4
import six

assert V(requests.__version__) >= V('2.4'), "Upgrade requests!" + _SEE_URL
assert V(six.__version__) >= V('1.5'), "Upgrade six!" + _SEE_URL
assert V(bs4.__version__) >= V('4.1'), "Upgrade bs4!" + _SEE_URL


def get_on_demand_video_url(session, video_id, subtitle_language='en',
                            resolution='540p'):
    """
    Return the download URL of on-demand course video.
    """

    url = OPENCOURSE_VIDEO_URL.format(video_id=video_id)
    page = get_page(session, url)

    logging.debug('Parsing JSON for video_id <%s>.', video_id)
    video_content = {}
    dom = json.loads(page)

    # videos
    logging.info('Gathering video URLs for video_id <%s>.', video_id)
    sources = dom['sources']
    sources.sort(key=lambda src: src['resolution'])
    sources.reverse()

    # Try to select resolution requested by the user.
    filtered_sources = [source
                        for source in sources
                        if source['resolution'] == resolution]

    if len(filtered_sources) == 0:
        # We will just use the 'vanilla' version of sources here, instead of
        # filtered_sources.
        logging.warn('Requested resolution %s not availaboe for <%s>. '
                     'Downloading highest resolution available instead.',
                     resolution, video_id)
    else:
        logging.info('Proceeding with download of resolution %s of <%s>.',
                     resolution, video_id)
        sources = filtered_sources

    video_url = sources[0]['formatSources']['video/mp4']
    video_content['mp4'] = video_url

    # subtitles and transcripts
    subtitle_nodes = [
        ('subtitles', 'srt', 'subtitle'),
        ('subtitlesTxt', 'txt', 'transcript'),
    ]
    for (subtitle_node, subtitle_extension, subtitle_description) in subtitle_nodes:
        logging.info('Gathering %s URLs for video_id <%s>.', subtitle_description, video_id)
        subtitles = dom.get(subtitle_node)
        if subtitles is not None:
            if subtitle_language == 'all':
                for current_subtitle_language in subtitles:
                    video_content[current_subtitle_language + '.' + subtitle_extension] = make_coursera_absolute_url(
                        subtitles.get(current_subtitle_language))
            else:
                if subtitle_language != 'en' and subtitle_language not in subtitles:
                    logging.warning("%s unavailable in '%s' language for video "
                                    "with video id: [%s], falling back to 'en' "
                                    "%s", subtitle_description.capitalize(), subtitle_language, video_id,
                                    subtitle_description)
                subtitle_language = 'en'

                subtitle_url = subtitles.get(subtitle_language)
                if subtitle_url is not None:
                    # some subtitle urls are relative!
                    video_content[subtitle_language + '.' + subtitle_extension] = make_coursera_absolute_url(
                        subtitle_url)

    return video_content


def get_page(session, url):
    """
    Download an HTML page using the requests session.
    """

    r = session.get(url)

    try:
        r.raise_for_status()
    except requests.exceptions.HTTPError as e:
        logging.error("Error %s getting page %s", e, url)
        raise

    return r.text


def get_session():
    """
    Create a session with TLS v1.2 certificate.
    """

    session = requests.Session()
    session.mount('https://', TLSAdapter())

    return session


def get_on_demand_syllabus(session, class_name):
    """
    Get the on-demand course listing webpage.
    """

    url = OPENCOURSE_CONTENT_URL.format(class_name=class_name)
    page = get_page(session, url)
    logging.info('Downloaded %s (%d bytes)', url, len(page))

    return page


def parse_on_demand_syllabus(session, page, reverse=False, intact_fnames=False,
                             subtitle_language='en', video_resolution=None):
    """
    Parse a Coursera on-demand course listing/syllabus page.
    """

    dom = json.loads(page)

    logging.info('Parsing syllabus of on-demand course. '
                 'This may take some time, be patient ...')
    modules = []
    json_modules = dom['courseMaterial']['elements']
    for module in json_modules:
        module_slug = module['slug']
        sections = []
        json_sections = module['elements']
        for section in json_sections:
            section_slug = section['slug']
            lectures = []
            json_lectures = section['elements']
            for lecture in json_lectures:
                lecture_slug = lecture['slug']
                if lecture['content']['typeName'] == 'lecture':
                    lecture_video_id = lecture['content']['definition']['videoId']
                    video_content = get_on_demand_video_url(session,
                                                            lecture_video_id,
                                                            subtitle_language,
                                                            video_resolution)
                    lecture_video_content = {}
                    for key, value in video_content.items():
                        lecture_video_content[key] = [(value, '')]

                    if lecture_video_content:
                        lectures.append((lecture_slug, lecture_video_content))

            if lectures:
                sections.append((section_slug, lectures))

        if sections:
            modules.append((module_slug, sections))

    if modules and reverse:
        modules.reverse()

    return modules


def is_course_complete(last_update):
    """
    Determine is the course is likely to have been terminated or not.

    We return True if the timestamp given by last_update is 30 days or older
    than today's date.  Otherwise, we return True.

    The intended use case for this is to detect if a given courses has not
    seen any update in the last 30 days or more.  Otherwise, we return True,
    since it is probably too soon to declare the course complete.
    """
    rv = False
    if last_update >= 0:
        delta = time.time() - last_update
        max_delta = total_seconds(datetime.timedelta(days=30))
        if delta > max_delta:
            rv = True
    return rv


def format_section(num, section, class_name, verbose_dirs):
    sec = '%02d_%s' % (num, section)
    if verbose_dirs:
        sec = class_name.upper() + '_' + sec
    return sec


def format_resource(num, name, title, fmt):
    if title:
        title = '_' + title
    return '%02d_%s%s.%s' % (num, name, title, fmt)


def format_combine_number_resource(secnum, lecnum, lecname, title, fmt):
    if title:
        title = '_' + title
    return '%02d_%02d_%s%s.%s' % (secnum, lecnum, lecname, title, fmt)


def find_resources_to_get(lecture, file_formats, resource_filter, ignored_formats=None):
    """
    Select formats to download.
    """
    resources_to_get = []

    if ignored_formats is None:
        ignored_formats = []

    if len(ignored_formats):
        logging.info("The following file formats will be ignored: " + ",".join(ignored_formats))

    for fmt, resources in iteritems(lecture):

        fmt0 = fmt
        if '.' in fmt:
            fmt = fmt.split('.')[1]

        if fmt in ignored_formats:
            continue

        if fmt in file_formats or 'all' in file_formats:
            for r in resources:
                if resource_filter and r[1] and not re.search(resource_filter, r[1]):
                    logging.debug('Skipping b/c of rf: %s %s',
                                  resource_filter, r[1])
                    continue
                resources_to_get.append((fmt0, r[0], r[1]))
        else:
            logging.debug(
                    'Skipping b/c format %s not in %s', fmt, file_formats)

    return resources_to_get


def download_lectures(downloader,
                      class_name,
                      sections,
                      file_formats,
                      overwrite=False,
                      skip_download=False,
                      section_filter=None,
                      lecture_filter=None,
                      resource_filter=None,
                      path='',
                      verbose_dirs=False,
                      preview=False,
                      combined_section_lectures_nums=False,
                      hooks=None,
                      playlist=False,
                      intact_fnames=False,
                      ignored_formats=None,
                      resume=False,
                      video_resolution='540p'):
    """
    Download lecture resources described by sections.

    Returns True if the class appears completed, False otherwise.
    """
    last_update = -1

    for (secnum, (section, lectures)) in enumerate(sections):
        if section_filter and not re.search(section_filter, section):
            logging.debug('Skipping b/c of sf: %s %s', section_filter,
                          section)
            continue

        sec = os.path.join(path, class_name,
                           format_section(secnum + 1, section, class_name, verbose_dirs))
        for (lecnum, (lecname, lecture)) in enumerate(lectures):
            if lecture_filter and not re.search(lecture_filter,
                                                lecname):
                logging.debug('Skipping b/c of lf: %s %s', lecture_filter,
                              lecname)
                continue

            if not os.path.exists(sec):
                mkdir_p(sec)

            resources_to_get = find_resources_to_get(lecture,
                                                     file_formats,
                                                     resource_filter,
                                                     ignored_formats)

            # write lecture resources
            for fmt, url, title in resources_to_get:

                if combined_section_lectures_nums:
                    lecfn = os.path.join(
                            sec,
                            format_combine_number_resource(
                                    secnum + 1, lecnum + 1, lecname, title, fmt))
                else:
                    lecfn = os.path.join(
                            sec, format_resource(lecnum + 1, lecname, title, fmt))

                if overwrite or not os.path.exists(lecfn) or resume:
                    if not skip_download:
                        logging.info('Downloading: %s', lecfn)
                        downloader.download(url, lecfn, resume=resume)
                    else:
                        open(lecfn, 'w').close()  # touch
                    last_update = time.time()
                else:
                    logging.info('%s already downloaded', lecfn)
                    # if this file hasn't been modified in a long time,
                    # record that time
                    last_update = max(last_update, os.path.getmtime(lecfn))

        # After fetching resources, create a playlist in M3U format with the
        # videos downloaded.
        if playlist:
            path_to_return = os.getcwd()

            for (_path, subdirs, files) in os.walk(sec):
                os.chdir(_path)
                globbed_videos = glob.glob("*.mp4")
                m3u_name = os.path.split(_path)[1] + ".m3u"

                if len(globbed_videos):
                    with open(m3u_name, "w") as m3u:
                        for video in globbed_videos:
                            m3u.write(video + "\n")
                    os.chdir(path_to_return)

        if hooks:
            for hook in hooks:
                logging.info('Running hook %s for section %s.', hook, sec)
                os.chdir(sec)
                subprocess.call(hook)

    # if we haven't updated any files in 1 month, we're probably
    # done with this course
    rv = is_course_complete(last_update)
    if rv:
        logging.info('COURSE PROBABLY COMPLETE: ' + class_name)
    return rv


def total_seconds(td):
    """
    Compute total seconds for a timedelta.

    Added for backward compatibility, pre 2.7.
    """
    return (td.microseconds +
            (td.seconds + td.days * 24 * 3600) * 10 ** 6) // 10 ** 6


def parse_args(args=None):
    """
    Parse the arguments/options passed to the program on the command line.
    """

    parser = argparse.ArgumentParser(
            description='Download Coursera.org lecture material and resources.')

    # Basic options
    group_basic = parser.add_argument_group('Basic options')

    group_basic.add_argument('class_names',
                             action='store',
                             nargs='+',
                             help='name(s) of the class(es) (e.g. "ml-005")')

    group_basic.add_argument('-u',
                             '--username',
                             dest='username',
                             action='store',
                             default=None,
                             help='coursera username')

    group_basic.add_argument('-p',
                             '--password',
                             dest='password',
                             action='store',
                             default=None,
                             help='coursera password')

    group_basic.add_argument('--on-demand',
                             dest='on_demand',
                             action='store_true',
                             default=False,
                             help='[DEPRECATED] get on-demand videos. Do not use'
                                  ' this option, it is deprecated. The script will'
                                  ' try to detect course type automatically.')

    group_basic.add_argument('-b',  # FIXME: kill this one-letter option
                             '--preview',
                             dest='preview',
                             action='store_true',
                             default=False,
                             help='get videos from preview pages. (Default: False)')

    group_basic.add_argument('--path',
                             dest='path',
                             action='store',
                             default='',
                             help='path to where to save the file. (Default: current directory)')

    group_basic.add_argument('-sl',  # FIXME: deprecate this option
                             '--subtitle-language',
                             dest='subtitle_language',
                             action='store',
                             default='all',
                             help='Choose language to download subtitles and transcripts. (Default: all)'
                                  'Use special value "all" to download all available.')

    # Selection of material to download
    group_material = parser.add_argument_group('Selection of material to download')

    group_material.add_argument('--about',  # FIXME: should be --about-course
                                dest='about',
                                action='store_true',
                                default=False,
                                help='download "about" metadata. (Default: False)')

    group_material.add_argument('-f',
                                '--formats',
                                dest='file_formats',
                                action='store',
                                default='all',
                                help='file format extensions to be downloaded in'
                                     ' quotes space separated, e.g. "mp4 pdf" '
                                     '(default: special value "all")')

    group_material.add_argument('--ignore-formats',
                                dest='ignore_formats',
                                action='store',
                                default=None,
                                help='file format extensions of resources to ignore'
                                     ' (default: None)')

    group_material.add_argument('-sf',  # FIXME: deprecate this option
                                '--section_filter',
                                dest='section_filter',
                                action='store',
                                default=None,
                                help='only download sections which contain this'
                                     ' regex (default: disabled)')

    group_material.add_argument('-lf',  # FIXME: deprecate this option
                                '--lecture_filter',
                                dest='lecture_filter',
                                action='store',
                                default=None,
                                help='only download lectures which contain this regex'
                                     ' (default: disabled)')

    group_material.add_argument('-rf',  # FIXME: deprecate this option
                                '--resource_filter',
                                dest='resource_filter',
                                action='store',
                                default=None,
                                help='only download resources which match this regex'
                                     ' (default: disabled)')

    group_material.add_argument('--video-resolution',
                                dest='video_resolution',
                                action='store',
                                default='540p',
                                help='video resolution to download (default: 540p); '
                                     'only valid for on-demand courses; '
                                     'only values allowed: 360p, 540p, 720p')

    # Selection of material to download
    group_external_dl = parser.add_argument_group('External downloaders')

    group_external_dl.add_argument('--wget',
                                   dest='wget',
                                   action='store',
                                   nargs='?',
                                   const='wget',
                                   default=None,
                                   help='use wget for downloading,'
                                        'optionally specify wget bin')
    group_external_dl.add_argument('--curl',
                                   dest='curl',
                                   action='store',
                                   nargs='?',
                                   const='curl',
                                   default=None,
                                   help='use curl for downloading,'
                                        ' optionally specify curl bin')
    group_external_dl.add_argument('--aria2',
                                   dest='aria2',
                                   action='store',
                                   nargs='?',
                                   const='aria2c',
                                   default=None,
                                   help='use aria2 for downloading,'
                                        ' optionally specify aria2 bin')
    group_external_dl.add_argument('--axel',
                                   dest='axel',
                                   action='store',
                                   nargs='?',
                                   const='axel',
                                   default=None,
                                   help='use axel for downloading,'
                                        ' optionally specify axel bin')

    parser.add_argument('--resume',
                        dest='resume',
                        action='store_true',
                        default=False,
                        help='resume incomplete downloads (default: False)')

    parser.add_argument('-o',
                        '--overwrite',
                        dest='overwrite',
                        action='store_true',
                        default=False,
                        help='whether existing files should be overwritten'
                             ' (default: False)')

    parser.add_argument('--verbose-dirs',
                        dest='verbose_dirs',
                        action='store_true',
                        default=False,
                        help='include class name in section directory name')

    parser.add_argument('--quiet',
                        dest='quiet',
                        action='store_true',
                        default=False,
                        help='omit as many messages as possible'
                             ' (only printing errors)')

    parser.add_argument('-r',
                        '--reverse',
                        dest='reverse',
                        action='store_true',
                        default=False,
                        help='download sections in reverse order')

    parser.add_argument('--combined-section-lectures-nums',
                        dest='combined_section_lectures_nums',
                        action='store_true',
                        default=False,
                        help='include lecture and section name in final files')

    parser.add_argument('--unrestricted-filenames',
                        dest='intact_fnames',
                        action='store_true',
                        default=False,
                        help='Do not limit filenames to be ASCII-only')

    # Advanced authentication
    group_adv_auth = parser.add_argument_group('Advanced authentication options')

    group_adv_auth.add_argument('-c',
                                '--cookies_file',
                                dest='cookies_file',
                                action='store',
                                default=None,
                                help='full path to the cookies.txt file')

    group_adv_auth.add_argument('-n',
                                '--netrc',
                                dest='netrc',
                                nargs='?',
                                action='store',
                                const=True,
                                default=False,
                                help='use netrc for reading passwords, uses default'
                                     ' location if no path specified')

    group_adv_auth.add_argument('-k',
                                '--keyring',
                                dest='use_keyring',
                                action='store_true',
                                default=False,
                                help='use keyring provided by operating system to '
                                     'save and load credentials')

    group_adv_auth.add_argument('--clear-cache',
                                dest='clear_cache',
                                action='store_true',
                                default=False,
                                help='clear cached cookies')

    # Advanced miscellaneous options
    group_adv_misc = parser.add_argument_group('Advanced miscellaneous options')

    group_adv_misc.add_argument('--hook',
                                dest='hooks',
                                action='append',
                                default=[],
                                help='hooks to run when finished')

    group_adv_misc.add_argument('-pl',
                                '--playlist',
                                dest='playlist',
                                action='store_true',
                                default=False,
                                help='generate M3U playlists for course weeks')

    # Debug options
    group_debug = parser.add_argument_group('Debugging options')

    group_debug.add_argument('--skip-download',
                             dest='skip_download',
                             action='store_true',
                             default=False,
                             help='for debugging: skip actual downloading of files')

    group_debug.add_argument('--debug',
                             dest='debug',
                             action='store_true',
                             default=False,
                             help='print lots of debug information')

    group_debug.add_argument('-l',  # FIXME: remove short option from rarely used ones
                             '--process_local_page',
                             dest='local_page',
                             help='uses or creates local cached version of syllabus'
                                  ' page')

    # Final parsing of the options
    args = parser.parse_args(args)

    # Initialize the logging system first so that other functions
    # can use it right away
    if args.debug:
        logging.basicConfig(level=logging.DEBUG,
                            format='%(name)s[%(funcName)s] %(message)s')
    elif args.quiet:
        logging.basicConfig(level=logging.ERROR,
                            format='%(name)s: %(message)s')
    else:
        logging.basicConfig(level=logging.INFO,
                            format='%(message)s')

    # turn list of strings into list
    args.file_formats = args.file_formats.split()

    # decode path so we can work properly with cyrillic symbols on different
    # versions on Python
    args.path = decode_input(args.path)

    # check arguments
    if args.use_keyring and args.password:
        logging.warning('--keyring and --password cannot be specified together')
        args.use_keyring = False

    if args.use_keyring and not keyring:
        logging.warning('The python module `keyring` not found.')
        args.use_keyring = False

    if args.cookies_file and not os.path.exists(args.cookies_file):
        logging.error('Cookies file not found: %s', args.cookies_file)
        sys.exit(1)

    if not args.cookies_file:
        try:
            args.username, args.password = get_credentials(
                    username=args.username, password=args.password,
                    netrc=args.netrc, use_keyring=args.use_keyring)
        except CredentialsError as e:
            logging.error(e)
            sys.exit(1)

    return args


def download_on_demand_class(args, class_name):
    """
    Download all requested resources from the on-demand class given in class_name.

    Returns True if the class appears completed.
    """

    session = get_session()
    login(session, args.username, args.password)

    # get the syllabus listing
    page = get_on_demand_syllabus(session, class_name)

    ignored_formats = []
    if args.ignore_formats:
        ignored_formats = args.ignore_formats.split(",")

    # parse it
    modules = parse_on_demand_syllabus(session, page,
                                       args.reverse,
                                       args.intact_fnames,
                                       args.subtitle_language,
                                       args.video_resolution)

    downloader = get_downloader(session, class_name, args)

    # obtain the resources
    completed = True
    for idx, module in enumerate(modules):
        module_name = '%02d_%s' % (idx + 1, module[0])
        sections = module[1]

        result = download_lectures(
                downloader,
                module_name,
                sections,
                args.file_formats,
                args.overwrite,
                args.skip_download,
                args.section_filter,
                args.lecture_filter,
                args.resource_filter,
                os.path.join(args.path, class_name),
                args.verbose_dirs,
                args.preview,
                args.combined_section_lectures_nums,
                args.hooks,
                args.playlist,
                args.intact_fnames,
                ignored_formats,
                args.resume
        )
        completed = completed and result

    return completed


def download_class(args, class_name):
    """
    Returns True if the class appears completed.
    """
    logging.debug('Downloading new style (on demand) class %s', class_name)
    return download_on_demand_class(args, class_name)


def main():
    """
    Main entry point for execution as a program (instead of as a module).
    """

    args = parse_args()
    completed_classes = []

    mkdir_p(PATH_CACHE, 0o700)
    if args.clear_cache:
        shutil.rmtree(PATH_CACHE)
    if args.on_demand:
        logging.warning('--on-demand option is deprecated and is not required'
                        ' anymore. Do not use this option. It will be removed'
                        'in the future.')

    for class_name in args.class_names:
        try:
            logging.info('Downloading class: %s', class_name)
            if download_class(args, class_name):
                completed_classes.append(class_name)
        except requests.exceptions.HTTPError as e:
            logging.error('HTTPError %s', e)
        except ClassNotFound as cnf:
            logging.error('Could not find class: %s', cnf)
        except AuthenticationFailed as af:
            logging.error('Could not authenticate: %s', af)

    if completed_classes:
        logging.info(
                "Classes which appear completed: " + " ".join(completed_classes))


if __name__ == '__main__':
    main()
