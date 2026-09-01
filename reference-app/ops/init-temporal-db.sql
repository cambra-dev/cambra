-- Temporal's auto-setup image creates its schema but not its databases when it
-- shares a Postgres instance with the application.
CREATE DATABASE temporal;
CREATE DATABASE temporal_visibility;
