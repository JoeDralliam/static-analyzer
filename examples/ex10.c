int x = rand(-100, 100);
int y = rand(-100, 100);
int z = rand(90, 300);
int f(int alpha, int beta)
{
    while(x >= alpha && x <= beta)
    {
	x++;
    }
}

int main()
{
    f(y, z);
    assert(x < y || x > z);
}
