#include "common.h"

__attribute__((noinline)) static void leakByteLocalFunction(itype leakThis, itype temp_) { temp_ = leakThis * SCALAR; }

void test3 (int idx, itype * a, itype temp_) {
    if (idx < SIZE) {
        leakByteLocalFunction(a[idx], temp_);
    }
}

int main () {

    TEMP
    PUBLICARRAY
    SECRETARRAY

    test3(SIZE, publicarray1, temp);
    
    return 0;
}