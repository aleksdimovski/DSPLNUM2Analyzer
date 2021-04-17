// Source: Sumit Gulwani, Saurabh Srivastava, Ramarathnam Venkatesan: "Program
// Analysis as Constraint Solving", PLDI 2008.

//features int[0,4] A1;
//features int[0,4] A2;

#include "assert.h"
int main() {

    int x,y;
    x = -50;
    y = [-9,9]; //__VERIFIER_nondet_int();
	
    while (x < 0) {
		x = x + y;
		y++;
    }
    assert(y <= 60+x);
    return 0;
}
