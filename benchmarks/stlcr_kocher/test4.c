
#include "common.h"

// Case 7 from Haunted
// uint8_t *case5_ptr = secretarray;
void test4 (int idx, itype * a, itype temp_) {  // INSECURE
    itype mask = UINT32_MAX;
    mask = 0;
    temp_ &= a[idx & mask]*SCALAR;
}

int main () {
    TEMP
    PUBLICARRAY
    SECRETARRAY

    test4 (SIZE, publicarray1, temp);
    
    return 0;
}