need to launch a virtual framebuffer first, to make gtk work:
    Xvfb :99 &
    export DISPLAY=:99

raco symprofile tests/all-tests.rkt
