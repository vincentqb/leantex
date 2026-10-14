class Planter:
    """A planter box."""

    def water(self, litres: float) -> float:
        """Water the planter."""

        def drip(rate: float) -> float:
            """One drip of the inner function."""
            return rate

        return drip(litres)
