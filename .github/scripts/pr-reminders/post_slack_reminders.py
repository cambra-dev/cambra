#!/usr/bin/env python3
"""Post stale review reminders to Slack as a thread.

Reads the JSON object find_stale_prs.py writes from stdin.

Required env: SLACK_BOT_TOKEN, SLACK_CHANNEL
Optional file: usermap.json (in working directory) for GitHub-to-Slack user resolution
"""

import argparse
import json
import os
import sys
from pathlib import Path

from prreminder import (
    GeneralReviewPr,
    StaleReview,
    build_thread_body,
    parse_iso,
    slack_post_message,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--failed", action="store_true",
                        help="Post a workflow-failure notice instead of reminders")
    args = parser.parse_args()

    token = os.environ["SLACK_BOT_TOKEN"]
    channel = os.environ["SLACK_CHANNEL"]

    if args.failed:
        slack_post_message(token, channel,
                           "Code Review Reminders!\n:sob: workflow failed! :sob:")
        return

    # Load usermap
    usermap_path = Path("usermap.json")
    if usermap_path.exists():
        usermap = json.loads(usermap_path.read_text())
    else:
        print("::warning::usermap.json not found, falling back to GitHub usernames",
              file=sys.stderr)
        usermap = {}

    found = json.load(sys.stdin)
    now = parse_iso(found["now"])
    general_review = [[GeneralReviewPr.from_dict(p) for p in group] for group in found["general_review"]]
    reviews = [StaleReview.from_dict(r) for r in found["reviews"]]

    # Build parent message
    if reviews or general_review:
        parent_text = "Code Review Reminders! :thread:"
    else:
        parent_text = "Code Review Reminders! :thread:\nNo stale reviews! :meow_party:"

    # Post parent message
    parent = slack_post_message(token, channel, parent_text)

    if not (reviews or general_review):
        print("No stale reviews. Posted all-clear to Slack.")
        return

    # Post threaded reply
    thread_ts = parent["ts"]
    channel_id = parent["channel"]
    body = build_thread_body(reviews, usermap, general_review=general_review, now=now)
    slack_post_message(token, channel_id, body, thread_ts=thread_ts)

    print("Reminders posted successfully.")


if __name__ == "__main__":
    main()
