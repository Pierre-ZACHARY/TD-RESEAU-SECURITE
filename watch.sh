#!/bin/sh
inotifywait -e modify,create -m ./*/*.c |
while read FILE EVENT; do
  frama-c -wp $FILE
done