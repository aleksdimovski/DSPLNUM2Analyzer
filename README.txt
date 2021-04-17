
This documents shows how to install the tool from the paper 
¨Lifted Static Analysis of Dynamic Program Families by Abstract Interpretation¨
if there is INTERNET CONNECTION 

###############################################################################
## DSPLNum^2Analyzer --- Lifted Static Analyzer for Dynamic Program Families ## 
###############################################################################

DSPLNum^2Analyzer is a research prototype lifted static analyzer based on abstract interpretation 
designed for performing numerical static analysis of dynamic C program families. 



## Author

	Aleksandar Dimovski (& Sven Apel)
	
	
# Installation

* Untar the given file:
	```
	tar -xvf DSPLNUM2Analyzer.tar.gz
	```

* Run the script install 
	```
	./install
	```	
	
*  Set the Library Path variable in ~/.bashrc 
	```
	gedit ~/.bashrc
	```
Then, set the Library Path by appending at the end of the file:
	```
	LD_LIBRARY_PATH=/home/username/.opam/default/share/apron/lib     % first find the folder where apron/lib is located
	export LD_LIBRARY_PATH
	```
Log out of the current session, then log in and check:
	```
	echo $LD_LIBRARY_PATH
	```

# Compiling DSPLNum^2Analyzer

Once all required libraries are installed, enter the folder 'DSPLNUM2Analyzer' and 'ocamlbuild' can be used to build lifted analyzer with the following command:

```
eval $(opam config env)                 % It will setup environment variables, that are necessary for the toolchain to work properly

ocamlbuild Main.native -use-ocamlfind -use-menhir -pkgs 'apron,gmp,oUnit,zarith' -I utils -I domains -I frontend -I main -libs boxMPQ,octD,polkaMPQ,str,zarith
```

# Usage

The analyzer performs a forward reachability analysis of dynamic program families.

The following general command-line options are recognized:

	 -single 							set to perform single-program analysis
	 -tree								set to perform decision tree-based lifted analysis
	 -domain boxes|octagons|polyhedra   set the abstract domain (defaults to boxes)
	 -minimal 							set to print only analysis result
	 -joinfwd 2                         set the widening delay in forward analysis


# Test example
'dfamily' example from "Motivating Example" section

enter the folder that contains the tool, and write

$ ./Main.native -single -domain boxes tests/dfamily-single.c  	// to perform single-program analysis using Interval (boxes) domain of "dfamily-single.c" file in the folder "tests"
$ ./Main.native -single -domain polyhedra tests/dfamily-single.c  // to perform single-program analysis using Polyhedra domain of "dfamily-single.c" file in the folder "tests"
$ ./Main.native -tree -domain boxes tests/dfamily-tree.c  	// to perform decision tree-based lifted analysis using Interval domain of "dfamily-tree.c" file in the folder "tests"
$ ./Main.native -tree -domain polyhedra tests/dfamily-tree.c  // to perform decision tree-based lifted analysis using Polyhedra domain of "dfamily-tree.c" file in the folder "tests"

########################################################################################################

