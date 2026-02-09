#!/usr/bin/env python3
"""Build a JSON mapping of GitHub usernames to Slack user IDs.

Uses each collaborator's public GitHub profile email to resolve their Slack ID.

Required env: GH_TOKEN, GH_REPOSITORY, SLACK_BOT_TOKEN
Output: writes usermap.json in the working directory
"""

import json
import os
import sys

from prreminder import get_user_email, list_collaborators, slack_lookup_email


def main() -> None:
    repo = os.environ["GH_REPOSITORY"]
    slack_token = os.environ["SLACK_BOT_TOKEN"]

    collaborators = list_collaborators(repo)
    usermap: dict[str, str] = {}

    for gh_user in collaborators:
        email = get_user_email(gh_user)
        if not email:
            print(f"::warning::No public email for {gh_user} "
                  "— they should set it to their @cambra.dev address")
            continue

        slack_id = slack_lookup_email(slack_token, email)
        if slack_id:
            print(f"Mapped {gh_user} -> {slack_id} (via {email})")
            usermap[gh_user] = slack_id
        else:
            print(f"::warning::Slack lookup failed for {gh_user} ({email})")

    with open("usermap.json", "w") as f:
        json.dump(usermap, f, indent=2)
        f.write("\n")

    print("Final user map:")
    print(json.dumps(usermap, indent=2))


if __name__ == "__main__":
    main()
