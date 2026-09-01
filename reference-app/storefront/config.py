"""Process configuration, read once from the environment."""

from functools import lru_cache

from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    model_config = SettingsConfigDict(env_file=".env", extra="ignore")

    database_url: str = "postgresql+asyncpg://storefront:storefront@localhost:5432/storefront"
    kafka_bootstrap: str = "localhost:9092"
    order_lines_topic: str = "storefront.order-lines"
    temporal_target: str = "localhost:7233"
    temporal_namespace: str = "default"
    task_queue: str = "storefront"

    payments_url: str = "http://localhost:8090"
    warehouse_url: str = "http://localhost:8090"
    email_url: str = "http://localhost:8090"

    object_store_root: str = "./data/objects"
    warehouse_path: str = "./data/warehouse/storefront.duckdb"

    promo_budget: int = 1000
    # Overridden to seconds in the integration tests so the abandonment timer
    # can be observed without a compressed-clock test server.
    abandon_after_seconds: int = 24 * 60 * 60

    etl_batch_max_rows: int = 500
    etl_batch_max_seconds: float = 5.0
    relay_poll_seconds: float = 0.5

    otlp_endpoint: str | None = None
    log_level: str = "INFO"


@lru_cache
def settings() -> Settings:
    return Settings()
