int main() {
    int a = 1;
    int b = 2;
    int c = 3;
    int d = 4;
    int e = 5;
    int f = 6;
    int g = 7;
    int h = 8;

    int res1 = (a + b) * c - d;
    int res2 = (e / f) + g % h;
    int res3 = res1 * res2 + (a - h);
    int res4 = (b + g) / (c - f);

    return res1 + res2 + res3 + res4;
}


