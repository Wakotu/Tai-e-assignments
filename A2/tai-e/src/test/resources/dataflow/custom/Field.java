class Foo {
  public int a;
}
/**
 * Field
 */
public class Field {
  public static void main(String[] args) {
    Foo foo = new Foo();
    foo.a = 10;
    int x = foo.a;
  }
}
