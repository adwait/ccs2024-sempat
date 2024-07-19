#include "common.h"

void test7 (int idx, itype * a, itype temp_) {
    itype last_idx = 0;
    if (idx == last_idx) {
        temp_ = a[idx] * SCALAR;
    }
    if (idx < SIZE) {
        last_idx = idx;
    }
}


int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test7 (SIZE, publicarray1, temp);
    
    return 0;
}