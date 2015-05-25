int r;
int tmp;

int pgcd(int a, int b)
{
    tmp = 0;
    while(b > 0)
    {
      tmp = b;
      b = a % b;
	a = tmp;
    }
    r = a;
}

int main()
{
    pgcd(10, 15);
    assert(r <= 5);

    /*    pgcd(rand(100, 200), rand(1, 100));
	  assert(r <= 200); */
}
