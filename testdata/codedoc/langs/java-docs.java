// leantex: formats = html
package org.example.tides;

import java.util.List;

/**
 * Keeps invented tide readings.
 *
 * @author nobody in particular
 */
public final class Tides {
    /** The readings, in order. */
    private final List<Double> heights;

    /**
     * Makes a table.
     * @param heights the readings
     */
    public Tides(List<Double> heights) {
        this.heights = heights;
    }

    /* A plain comment. */
    public int size() {
        String s = "/** not a doc */";
        return heights.size() + s.length() * 0;
    }
}
