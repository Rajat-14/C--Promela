proctype gcd(chan in_gcd; int a; int b)
{
    chan ret_gcd = [0] of {int};
    int tmp;
    if
    :: (b == 0) ->
        in_gcd ! a;
        goto end;
    :: else ->
        run gcd(ret_gcd, b, a % b);
        ret_gcd ? tmp;
        in_gcd ! tmp;
        goto end;
    fi;
end:
    
}

proctype main(chan in_main)
{
    int x = 48;
    int y = 18;
    chan ret_main = [0] of {int};
    int result;
    run gcd(ret_main, x, y);
    ret_main ? result;
    printf("GCD of %d and %d is %d\n", x, y, result);
    in_main ! 0;
}

init
{
    chan ret_main = [0] of {int};
    int result;
    run main(ret_main);
    ret_main ? result;
}
