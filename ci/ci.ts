import { format, github, job, workflow } from "@dedalus-labs/hollywood";

const checkout = {
	name: "Checkout",
	uses: "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
	with: { "persist-credentials": false },
} as const;

export const ci = workflow({
	name: "CI",
	on: {
		push: { branches: ["main"] },
		pull_request: {},
		merge_group: { types: ["checks_requested"] },
		workflow_dispatch: {},
	},
	permissions: {},
	concurrency: {
		group: format("{0}-{1}", github.workflow, github.ref),
		"cancel-in-progress": true,
	},
	env: { FORCE_JAVASCRIPT_ACTIONS_TO_NODE24: true },
	jobs: {
		workflows: job({
			name: "Generated workflows",
			"runs-on": "ubuntu-24.04",
			"timeout-minutes": 10,
			permissions: { contents: "read" },
			steps: [
				checkout,
				{
					name: "Set up Node",
					uses: "actions/setup-node@249970729cb0ef3589644e2896645e5dc5ba9c38",
					with: { "node-version": "26.5.1" },
				},
				{ name: "Install dependencies", run: "npm ci --ignore-scripts" },
				{ name: "Audit dependencies", run: "npm audit --audit-level=high" },
				{ name: "Check workflow source", run: "npm run check" },
				{
					name: "Set up Terraform",
					uses: "hashicorp/setup-terraform@dfe3c3f87815947d99a8997f908cb6525fc44e9e",
					with: { terraform_version: "1.14.4" },
				},
				{
					name: "Check repository controls",
					run: [
						"terraform -chdir=iac/github fmt -check",
						"terraform -chdir=iac/github init -backend=false -input=false -lockfile=readonly",
						"terraform -chdir=iac/github validate",
					].join("\n"),
				},
			],
		}),
		lean: job({
			name: "Lean",
			"runs-on": "ubuntu-24.04",
			"timeout-minutes": 30,
			permissions: {
				contents: "read",
				pages: "write",
				"id-token": "write",
			},
			steps: [
				checkout,
				{
					name: "Build and lint",
					uses: "leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9",
					with: {
						"build-args": "--wfail",
						lint: "true",
						"use-github-cache": "true",
						"use-mathlib-cache": "true",
					},
				},
				{
					name: "Build documentation",
					uses: "leanprover-community/docgen-action@56dff2bb89f3e9b8c1b6d5c8410362c19de2d904",
				},
			],
		}),
	},
});
