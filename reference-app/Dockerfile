FROM python:3.13-slim

ENV PYTHONUNBUFFERED=1 PIP_NO_CACHE_DIR=1

WORKDIR /app
COPY pyproject.toml README.md ./
COPY storefront ./storefront
RUN pip install --no-cache-dir -e ".[dev]"
COPY alembic.ini ./
COPY migrations ./migrations
COPY tests ./tests

CMD ["uvicorn", "storefront.api.main:app", "--host", "0.0.0.0", "--port", "8080"]
