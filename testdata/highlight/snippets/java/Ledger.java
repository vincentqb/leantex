package org.example.ledger;

import java.util.ArrayList;
import java.util.List;
import static java.lang.Math.max;

/**
 * Keeps an invented ledger of entries.
 *
 * @param <T> the kind of amount
 */
public final class Ledger<T extends Number> implements Iterable<T> {
    private final List<T> entries = new ArrayList<>();
    protected static final long LIMIT = 1_000_000L;

    /** A note attached to an entry. */
    public record Note(String text, int line) {}

    public enum Kind { CREDIT, DEBIT }

    @Override
    public java.util.Iterator<T> iterator() {
        return entries.iterator();
    }

    /**
     * Adds an amount.
     * @param amount the amount to add
     * @return whether it was added
     */
    public synchronized boolean add(T amount) throws IllegalStateException {
        if (amount == null) {
            throw new IllegalStateException("no amount");
        }
        return entries.add(amount);
    }

    public double total() {
        double sum = 0.0d;
        for (T e : this) sum += e.doubleValue();
        return max(sum, 0x1p-3);
    }

    public static void main(String[] args) {
        var ledger = new Ledger<Integer>();
        char c = '\n';
        int hex = 0xCAFE, bin = 0b1011, oct = 017;
        float f = 3.5e2f;
        String block = """
            a text block
            with "quotes"
            """;
        outer:
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "skip": continue outer;
                default: ledger.add(i);
            }
        }
        System.out.println(ledger.total() + " " + c + hex + bin + oct + f + block);
    }
}
