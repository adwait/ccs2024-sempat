
#include "common.h"

// case 3 from Haunted
void test2 (int idx, itype * a, int temp_) { // SECURE
    register itype ridx asm ("a6");
    ridx = idx & (SIZE-1);

    /* Access overwritten secret */
    temp_ &= a[ridx]*SCALAR;  
}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test2(SIZE, publicarray1, temp);
    
    return 0;

}