#wiring problem

**Author:** Cesar Pinera

This is a solution for the wiring problem for CS541

##Requirements:
- A running JVM 1.7 or newer. It may run on 1.6, but that is untested.
- Leiningen 2. Please see the http://leiningen.org site for instructions on how to install it. 
- Linux or Mac OS X. Tested with the later.

##Usage:

````
lein run [filename or url]
````

Example:

````
lein run http://svcs.cs.pdx.edu/circuit-wiring/inst-3.txt
````

##Output:

The program will use internally SAT4J, a SAT solver for Java. If a solution is found, it will be printed on the console. If no solution is found, it will be indicated in the console.

##License:

This is free and unencumbered software released into the public domain.
