#! /bin/sh

scala_lib=/usr/share/java/scala-library-2.9.1.jar
java -cp $scala_lib:bin Main "$@"
