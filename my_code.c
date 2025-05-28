#include <stdio.h>

int gcd(int a, int b)
{
    if (b == 0)
        return a;
    return gcd(b, a % b);
}

int main()
{
    int x = 48, y = 18;
    int result = gcd(x, y);
    printf("GCD of %d and %d is %d\n", x, y, result);
    return 0;
}