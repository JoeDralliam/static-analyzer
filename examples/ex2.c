int x = rand(-100, 24), y;
int main()
{
    while(x <= 50)
    {
	x += 2;
	y += 1;
    }
    assert(50 < x && x <= 52);
}
