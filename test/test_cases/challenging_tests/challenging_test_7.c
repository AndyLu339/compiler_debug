int main() {
    int x = 1;
    int y = 0;
    int z = 1;
    int a = 10;
    int b = 20;
    int complex_logic_res = 0;
    if ((x == 1 && y == 1) || (z == 1 && a > b)) {
        complex_logic_res = 1;
    } else {
        complex_logic_res = 0;
    }
    return complex_logic_res;
}


