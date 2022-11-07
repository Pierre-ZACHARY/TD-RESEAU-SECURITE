#!/bin/sh
inotifywait -e modify,create -m ./**.c |
while read FILE EVENT; do
  echo $FILE
  frama-c -wp -wp-rte $FILE
done