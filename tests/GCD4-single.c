//features int[0,4] A1;
//features int[0,4] A2;
//features int[0,4] A3;

typedef enum {false,true} bool;


int main() {
    int x;
    int y;
    int tmp;
    int xtmp;
	
    x = [-9,9]; //__VERIFIER_nondet_int();
    y = [-9,9]; // __VERIFIER_nondet_int();
    
    while(y > 0 && x > 0) {
        tmp = y;
        xtmp = x;
        
        while(xtmp>=y && y > 0) {
            xtmp = xtmp - y;
        }
        
        y = xtmp;
        x = tmp;
    }
    
    return 0;
}