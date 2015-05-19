int x = rand(-100, 100);
int y = rand(-100, 100);

int f(int alpha)
{
    if(x == alpha)
    {
	x = alpha + 1;
    }
}

int main()
{
    f(y);
    assert(x != y);
}
