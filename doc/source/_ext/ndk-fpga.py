import os


def build_init(app):
    os.symlink(app.srcdir + '/../../apps', app.srcdir + '/ndk_apps')
    os.symlink(app.srcdir + '/../../core', app.srcdir + '/ndk_core')
    os.symlink(app.srcdir + '/../../build', app.srcdir + '/ndk_build')
    os.symlink(app.srcdir + '/../../cards', app.srcdir + '/ndk_cards')
    os.symlink(app.srcdir + '/../../extra', app.srcdir + '/ndk_extra')
    os.symlink(app.srcdir + '/../../comp', app.srcdir + '/comp')


def build_finish(app, exception):
    os.remove(app.srcdir + '/ndk_apps')
    os.remove(app.srcdir + '/ndk_core')
    os.remove(app.srcdir + '/ndk_build')
    os.remove(app.srcdir + '/ndk_cards')
    os.remove(app.srcdir + '/ndk_extra')
    os.remove(app.srcdir + '/comp')


def setup(app):
    app.connect('builder-inited', build_init)
    app.connect('build-finished', build_finish)

    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
