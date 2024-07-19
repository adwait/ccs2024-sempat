#include "common.h"

static void leakByteLocalFunction(itype leakThis, itype temp_) { temp_ = leakThis * SCALAR; }

void test2 (int idx, itype * a, itype temp_) {
    if (idx < SIZE) {
        leakByteLocalFunction(a[idx], temp_);
    }
}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test2(SIZE, publicarray1, temp);
    
    return 0;
}