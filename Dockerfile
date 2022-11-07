FROM framac/frama-c:25.0

RUN sudo apk add inotify-tools

WORKDIR /workspace/

ENTRYPOINT bash watch.sh