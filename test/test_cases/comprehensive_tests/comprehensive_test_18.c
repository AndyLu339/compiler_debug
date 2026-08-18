
int main() {
    int f0 = 0;
    int f1 = 1;
    int fn = 0;
    int i = 2;
    while (i < 10) {
        fn = f0 + f1;
        f0 = f1;
        f1 = fn;
        i = i + 1;
    }
    return fn;
}


