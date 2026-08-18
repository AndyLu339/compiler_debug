int get_five() {
    return 5;
}
int main() {
    int a = 10;
    int b = 5;
    int result = 0;
    result = (a + b) * (a - b) / 2 + get_five();
    return result;
}


