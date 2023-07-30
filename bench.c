#include <stdio.h>
#include <stdlib.h>

int main () {

    extern int _c0_main();

    printf("started\n");

    int i = _c0_main();

    printf("done %d\n", i);

    return 0;
}