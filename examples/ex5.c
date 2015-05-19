int x = rand(-100, 100);

int main()
{
    if(x == 0)
    {
	x = 1;
    }
    assert(x != 1);
}
