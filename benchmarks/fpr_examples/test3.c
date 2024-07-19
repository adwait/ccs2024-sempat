#define ADDR_MAX 0x10

int main () {

    int a[ADDR_MAX];
    int b[ADDR_MAX];
    
    register int _temp asm("a5");
    _temp = a[0];
    a[1] = 1;
    int c = b[_temp];

    return 0;
}