int get_five() {
    return 5;
}
int main() {
    int a = 10;
    int b = 5;
    int c = 0;
    int result = 0;
    if ((a > 5 || b < 3) && (c == 0 && a != b) || (get_five() == 5)) {
        result = 1;
    } else {
        result = 0;
    }
    return result;
}


