int u, v, w;
int z = 0;


int f(int x, int y)
{
    z = 2 * x;
    return z + y - x;
}

int main()
{
    u = 4;
    f(u, 10);
    v = 5;
    w = 3;
    v = f(w, v);
}
