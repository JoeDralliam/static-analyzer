int tmp;

int f(int x, int y, int z)
{
    for(;x < 10; x++){}
    return x * y + z;
}

int main()
{
    tmp  = f(3,4, 3);
}
