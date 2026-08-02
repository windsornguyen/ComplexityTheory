locals {
  repository = "ComplexityTheory"
}

provider "github" {
  owner = "windsornguyen"
}

resource "github_repository" "this" {
  name        = local.repository
  description = "A formalization of computational complexity theory in Lean"
  visibility  = "public"

  has_discussions = true
  has_issues      = true
  has_projects    = false
  has_wiki        = false

  allow_auto_merge       = true
  allow_merge_commit     = false
  allow_rebase_merge     = false
  allow_squash_merge     = true
  delete_branch_on_merge = true

  squash_merge_commit_message = "PR_BODY"
  squash_merge_commit_title   = "PR_TITLE"
  archive_on_destroy          = true
}

resource "github_actions_repository_permissions" "this" {
  repository      = github_repository.this.name
  enabled         = true
  allowed_actions = "selected"

  # lean-action composes GitHub-owned cache actions by major tag. Hollywood
  # still enforces immutable refs for every action declared in our workflows.
  sha_pinning_required = false

  allowed_actions_config {
    github_owned_allowed = true
    patterns_allowed = [
      "googleapis/release-please-action@*",
      "hashicorp/setup-terraform@*",
      "leanprover-community/docgen-action@*",
      "leanprover/lean-action@*",
      "ruby/setup-ruby@*",
      "xu-cheng/texlive-action@*",
    ]
    verified_allowed = false
  }
}

resource "github_workflow_repository_permissions" "this" {
  repository                       = github_repository.this.name
  default_workflow_permissions     = "read"
  can_approve_pull_request_reviews = true
}

resource "github_repository_vulnerability_alerts" "this" {
  repository = github_repository.this.name
  enabled    = true
}

resource "github_repository_dependabot_security_updates" "this" {
  repository = github_repository.this.name
  enabled    = true

  depends_on = [github_repository_vulnerability_alerts.this]
}

resource "github_repository_ruleset" "main" {
  repository  = github_repository.this.name
  name        = "main"
  target      = "branch"
  enforcement = "active"

  conditions {
    ref_name {
      include = ["refs/heads/main"]
      exclude = []
    }
  }

  rules {
    deletion                = true
    non_fast_forward        = true
    required_linear_history = true

    pull_request {
      allowed_merge_methods             = ["squash"]
      dismiss_stale_reviews_on_push     = false
      require_code_owner_review         = false
      require_last_push_approval        = false
      required_approving_review_count   = 0
      required_review_thread_resolution = true
    }

    required_status_checks {
      do_not_enforce_on_create             = false
      strict_required_status_checks_policy = false

      required_check {
        context = "Generated workflows"
      }

      required_check {
        context = "Lean"
      }
    }
  }
}

import {
  to = github_repository.this
  id = local.repository
}

import {
  to = github_actions_repository_permissions.this
  id = local.repository
}

import {
  to = github_workflow_repository_permissions.this
  id = local.repository
}
