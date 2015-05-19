int x = rand(-100, 100);

int f(int alpha)
{
    if(x == alpha)
    {
	x = alpha + 1;
    }
    else
    {
	x = alpha;
    }
}

int main()
{
    f(9);
    assert(x != 10);
}
