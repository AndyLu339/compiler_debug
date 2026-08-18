
int get_val(int input) {
    if (input == 1) return 10;
    if (input == 2) return 20;
    if (input == 3) return 30;
    return 0;
}
int main() {
    int res1 = get_val(1);
    int res2 = get_val(2);
    int res3 = get_val(3);
    int res4 = get_val(4);
    return res1 + res2 + res3 + res4;
}


