int x = rand(0, 100);
int y = rand(0, 100);
int d = 0;
int main()
{
    if (x <= y)
    {
	y = x;
    }
    d = x - y;
    assert (d >= 0);
    return 5;
}
