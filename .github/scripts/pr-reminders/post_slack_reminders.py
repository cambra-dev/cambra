#!/usr/bin/env python3
"""Post stale review reminders to Slack as a thread.

Reads JSONL from stdin (one StaleReview per line).

Required env: SLACK_BOT_TOKEN, SLACK_CHANNEL
Optional file: usermap.json (in working directory) for GitHub-to-Slack user resolution
"""

import json
import os
import sys
from pathlib import Path

from prreminder import (
    StaleReview,
    build_thread_body,
    slack_post_message,
)


def main() -> None:
    token = os.environ["SLACK_BOT_TOKEN"]
    channel = os.environ["SLACK_CHANNEL"]

    # Load usermap
    usermap_path = Path("usermap.json")
    if usermap_path.exists():
        usermap = json.loads(usermap_path.read_text())
    else:
        print("::warning::usermap.json not found, falling back to GitHub usernames",
              file=sys.stderr)
        usermap = {}

    # Read JSONL from stdin
    reviews = []
    for line in sys.stdin:
        line = line.strip()
        if line:
            reviews.append(StaleReview.from_dict(json.loads(line)))

    # Build parent message
    if reviews:
        parent_text = "Code Review Reminders! :thread:"
    else:
        parent_text = "Code Review Reminders! :thread:\nNo stale reviews! :meow_party:"

    # Post parent message
    parent = slack_post_message(token, channel, parent_text)

    if not reviews:
        print("No stale reviews. Posted all-clear to Slack.")
        return

    # Post threaded reply
    thread_ts = parent["ts"]
    channel_id = parent["channel"]
    body = build_thread_body(reviews, usermap)
    slack_post_message(token, channel_id, body, thread_ts=thread_ts)

    print("Reminders posted successfully.")


if __name__ == "__main__":
    main()
