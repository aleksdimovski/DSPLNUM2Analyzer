# DSPLNUM2Analyzer --- Lifted Analyses Tool for Dynamic SPLs with Boolean and Numerical Features

This tool is a research prototype static analyzer designed for performing numerical static analyzes of dynamic C program families. 


## Author

	
	
# Installation

The tool requires the following applications and libraries:

* OCaml 

	```
	(sudo) apt-get install ocaml-interp
	```

* Findlib

	```
	(sudo) apt-get install ocaml-findlib
	```

* Menhir: LR(1) parser generator

	```
	(sudo) apt-get install menhir
	```
  
* Opam: https://opam.ocaml.org/doc/Install.html

	```
	(sudo) apt-get install opam
	```
* Initialize OPAM state
	```
	opam init      % during initilization allow opam to modify ~/.profile
	```	
	```
	eval $(opam env)      % update the current shell environment
	```  
	
* OUnit

	```
	opam install ounit
	```

* APRON: numerical abstract domain library

	```
	opam install depext
	opam depext apron
	opam install apron
	```
*  Set the Library Path variable in ~/.bashrc 
	```
	gedit ~/.bashrc"
	```
Then, set the Library Path by appending:
	```
	LD_LIBRARY_PATH=/home/username/.opam/default/share/apron/lib     % first find the folder where apron/lib is located
	export LD_LIBRARY_PATH
	```
Log out of the current session, then log in and check:
	```
	echo $LD_LIBRARY_PATH
	```

* Zarith: arbitrary-precision integer operations

	```
	opam install zarith
	```


# Compiling lifted_analyzer

Once all required libraries are installed, 'ocamlbuild' can be used to build lifted_analyzer with the following command:

```
eval $(opam config env)                 % It will setup environment variables, that are necessary for the toolchain to work properly

ocamlbuild Main.native -use-ocamlfind -use-menhir -pkgs 'apron,gmp,oUnit,zarith' -I utils -I domains -I frontend -I main -libs boxMPQ,octD,polkaMPQ,str,zarith
```

# Usage

The analyzer performs a forward reachability analysis of dynamic program families.

The following general command-line options are recognized
(showing their default value):

	 -single 							set to perform single-program analysis
	 -tree								set to perform decision tree-based lifted analysis
	 -domain boxes|octagons|polyhedra   set the abstract domain (defaults to boxes)
	 -minimal 							set to print only analysis result
	 -joinfwd 2                         set the widening delay in forward analysis


# Examples from the paper:

1. 'dfamily' example from "Motivating Example" section

enter the folder that contains the tool, and write

$ ./Main.native -single -domain boxes tests/dfamily-single.c  	// to perform single lifted analysis using Interval domain of the dfamily-single file in the folder tests
$ ./Main.native -single -domain polyhedra tests/dfamily-single.c  // to perform single lifted analysis using Polyhedra domain of the dfamily-single file in the folder tests
$ ./Main.native -tree -domain boxes tests/dfamily-tree.c  	// to perform decision tree-based lifted analysis using Interval domain of the dfamily-tree file in the folder tests
$ ./Main.native -tree -domain polyhedra tests/dfamily-tree.c  // to perform decision tree-based lifted analysis using Polyhedra domain of the dfamily-tree file in the folder tests


2. Example 5

$ ./Main.native -tree -domain polyhedra tests/example5-tree.c 
$ ./Main.native -single -domain polyhedra tests/example5-single.c 


3. Example8

$ ./Main.native -tree -domain polyhedra tests/example8-tree.c 
$ ./Main.native -single -domain polyhedra tests/example8-single.c 


4. Benchmarks from Table 1, E-mail system

Since the output is huge, we use '-minimal' option to print out only the analysis result
We send the output in a textual file for more easier searching through it

./Main.native -single -domain boxes -minimal spl-tests/email_spec0-single.c > spec0-single.out 
./Main.native -tree -domain boxes -minimal spl-tests/email_spec0-feat1.c > spec0-feat1.out
./Main.native -tree -domain boxes -minimal spl-tests/email_spec0-feat2.c > spec0-feat2.out

./Main.native -single -domain boxes -minimal spl-tests/email_spec6-single.c > spec6-single.out 
./Main.native -tree -domain boxes -minimal spl-tests/email_spec6-feat1.c > spec6-feat1.out
./Main.native -tree -domain boxes -minimal spl-tests/email_spec6-feat2.c > spec6-feat2.out

./Main.native -single -domain boxes -minimal spl-tests/email_spec8-single.c > spec8-single.out 
./Main.native -tree -domain boxes -minimal spl-tests/email_spec8-feat1.c > spec8-feat6.out
./Main.native -tree -domain boxes -minimal spl-tests/email_spec8-feat2.c > spec8-feat6.out

./Main.native -single -domain boxes -minimal spl-tests/email_spec11-single.c > spec11-single.out 
./Main.native -tree -domain boxes -minimal spl-tests/email_spec11-feat1.c > spec11-feat6.out
./Main.native -tree -domain boxes -minimal spl-tests/email_spec11-feat2.c > spec11-feat6.out

./Main.native -single -domain boxes -minimal spl-tests/email_spec27-single.c > spec27-single.out 
./Main.native -tree -domain boxes -minimal spl-tests/email_spec27-feat1.c > spec27-feat6.out
./Main.native -tree -domain boxes -minimal spl-tests/email_spec27-feat2.c > spec27-feat6.out


5. Benchmarks from Table 2, Other categories

./Main.native -single -domain polyhedra tests/half_2-single.c 
./Main.native -tree -domain polyhedra tests/half_2-tree.c
./Main.native -tree -domain octagons tests/half_2-tree.c

./Main.native -single -domain polyhedra tests/seq-single.c 
./Main.native -tree -domain polyhedra tests/seq-tree.c
./Main.native -tree -domain octagons tests/seq-tree.c

./Main.native -single -domain polyhedra tests/sum01_bug02-single.c 
./Main.native -tree -domain polyhedra tests/sum01_bug02-tree.c
./Main.native -tree -domain octagons tests/sum01_bug02-tree.c
./Main.native -tree -domain boxes tests/sum01_bug02-tree.c

./Main.native -single -domain polyhedra tests/count_up_down-single.c 
./Main.native -tree -domain polyhedra tests/count_up_down-tree.c
./Main.native -tree -domain octagons tests/count_up_down-tree.c

./Main.native -single -domain polyhedra tests/hhk2008-single.c 
./Main.native -tree -domain polyhedra tests/hhk2008-tree.c
./Main.native -tree -domain octagons tests/hhk2008-tree.c

./Main.native -single -domain polyhedra tests/gsv2008-single.c 
./Main.native -tree -domain polyhedra tests/gsv2008-tree.c
./Main.native -tree -domain octagons tests/gsv2008-tree.c

./Main.native -single -domain polyhedra tests/Mysore-single.c 
./Main.native -tree -domain polyhedra tests/Mysore-tree.c
./Main.native -tree -domain octagons tests/Mysore-tree.c

./Main.native -single -domain polyhedra tests/Copenhagen-single.c 
./Main.native -tree -domain polyhedra tests/Copenhagen-tree.c
./Main.native -tree -domain octagons tests/Copenhagen-tree.c