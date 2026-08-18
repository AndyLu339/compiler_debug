int get_five() {
    return 5;
}
int add(int p1, int p2) {
    return p1 + p2;
}
int main() {
    int result = 0;
    result = add(get_five(), get_five());
    return result;
}


