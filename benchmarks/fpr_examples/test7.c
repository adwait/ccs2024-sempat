#define ADDR_MAX 0x80

int main () {

    int a[ADDR_MAX];
    int b[ADDR_MAX];
    
    register int _temp asm("a5");
    _temp = a[0];
    a[16] = 1;
    int c = b[_temp];

    return 0;
}