
int get_five() {
    return 5;
}
int main() {
    int b = 5;
    int c = 0;
    if (get_five() == b) {
        c = 100;
    } else {
        c = 200;
    }
    return c;
}


