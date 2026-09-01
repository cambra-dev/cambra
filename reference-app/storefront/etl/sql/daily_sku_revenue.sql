-- The mart: revenue and units per day and SKU.
CREATE OR REPLACE TABLE daily_sku_revenue AS
SELECT
    CAST(ingested_at AS DATE) AS day,
    sku,
    SUM(price)                AS revenue,
    SUM(qty)                  AS units
FROM raw_order_lines
GROUP BY 1, 2;
