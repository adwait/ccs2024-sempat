
#include "common.h"

// Case 5 from Haunted
// uint8_t *case5_ptr = secretarray;
void test3 (int idx, itype * a, itype * b, itype temp_) {  // INSECURE
    register itype ridx asm ("a6");
    ridx = idx & 0;

    b = a;       // Bypassed store

    temp_ &= b[ridx]*SCALAR;
}

int main () {
    TEMP
    PUBLICARRAY
    SECRETARRAY

    test3(SIZE, publicarray1, secretarray, temp);
    
    return 0;
}