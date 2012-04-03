#! /bin/sh

scoqc=/usr/local/coq-8.3pl2-with-scala/bin/coqc
scala_lib=/usr/share/java/scala-library-2.9.1.jar
mkdir -p bin
$scoqc Reverse.v
scalac -d bin Coq.scala Main.java
javac  -d bin -cp $scala_lib:bin Main.java

