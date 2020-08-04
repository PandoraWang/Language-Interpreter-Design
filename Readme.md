###Overview

The goal of this project is to understand and build an interpreter in two languages(Ocaml & Python)for a small OCaml-like, stack based, bytecode language. 
These files  contain a function (static method in Java) called interpreter that takes two strings (interpreter(input, ouput)). 

### Functionality

 Interpreter function (or static method) should take in two arguments, the file you are reading from (input) and the file name of your output file (output).

```oca
val interpreter : string -> string -> unit = <fun>
public static void interpreter (String inputFile, String outputFile){} 
def interpreter(inputFile, outputFile):
```

### Grammar

The following is a context free grammar for the bytecode language you will be implementing.