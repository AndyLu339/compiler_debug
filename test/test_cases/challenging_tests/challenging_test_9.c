int main() {
    int a = 10;
    int c = 0;
    {
        int local_var = 100;
        c = local_var;
    }
    c = a;
    return c;
}


