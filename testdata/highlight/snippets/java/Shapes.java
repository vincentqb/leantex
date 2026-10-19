// A sealed hierarchy of invented shapes.
sealed interface Shape permits Circle, Square {}
record Circle(double r) implements Shape {}
record Square(double side) implements Shape {}
@FunctionalInterface
interface Area { double of(Shape s); }
class Areas {
    static final Area AREA = s -> switch (s) {
        case Circle c -> Math.PI * c.r() * c.r();
        case Square q -> q.side() * q.side();
    };
    /* plain block comment */
    int[] counts = {1, 2, 3};
    transient volatile Object lock = new Object();
}
