import os

def build_init(app):
    os.symlink(app.srcdir + '/../../app', app.srcdir + '/app')
    os.symlink(app.srcdir + '/../../ndk/cards', app.srcdir + '/ndk_cards')
    os.symlink(app.srcdir + '/../../ndk/core', app.srcdir + '/ndk_core')
    os.symlink(app.srcdir + '/../../ndk/ofm/build', app.srcdir + '/../../ndk/ofm/doc/source/build')
    os.symlink(app.srcdir + '/../../ndk/ofm/comp', app.srcdir + '/../../ndk/ofm/doc/source/comp')
    os.symlink(app.srcdir + '/../../ndk/ofm/doc/source', app.srcdir + '/ofm_doc')

def build_finish(app, exception):
    os.remove(app.srcdir + '/app')
    os.remove(app.srcdir + '/ndk_cards')
    os.remove(app.srcdir + '/ndk_core')
    os.remove(app.srcdir + '/../../ndk/ofm/doc/source/build')
    os.remove(app.srcdir + '/../../ndk/ofm/doc/source/comp')
    os.remove(app.srcdir + '/ofm_doc')

def setup(app):
    app.connect('builder-inited', build_init)
    app.connect('build-finished', build_finish)

    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
