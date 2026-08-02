import { job, workflow } from "@dedalus-labs/hollywood";

const checkout = "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1";
const deployPages = "actions/deploy-pages@cd2ce8fcbc39b97be8ca5fce6e763baed58fa128";
const leanAction = "leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9";
const setupPython = "actions/setup-python@a309ff8b426b58ec0e2a45f0f869d46889d02405";
const uploadPages = "actions/upload-pages-artifact@7b1f4a764d45c48632c6b24a0339c27f5614fb0b";

const docsPaths = [
	"**/*.lean",
	"docbuild/**",
	"docs/**",
	"lake-manifest.json",
	"lakefile.toml",
	"lean-toolchain",
	"mkdocs.yml",
] as const;

export const docs = workflow({
	name: "Docs",
	on: {
		push: { branches: ["main"], paths: docsPaths },
		pull_request: { branches: ["main"], paths: docsPaths },
		workflow_dispatch: {},
	},
	permissions: { contents: "read" },
	concurrency: { group: "pages", "cancel-in-progress": false },
	jobs: {
		build: job({
			name: "Documentation",
			"runs-on": "ubuntu-24.04",
			"timeout-minutes": 30,
			steps: [
				{ uses: checkout, with: { "persist-credentials": false } },
				{
					name: "Set up Lean",
					uses: leanAction,
					with: {
						"auto-config": "false",
						build: "false",
						lint: "false",
						test: "false",
						"use-github-cache": "false",
						"use-mathlib-cache": "true",
					},
				},
				{
					name: "Set up Python",
					uses: setupPython,
					with: { "python-version": "3.13" },
				},
				{
					name: "Install documentation dependencies",
					run: "python -m pip install -r docs/requirements.txt",
				},
				{
					name: "Build Lean API documentation",
					run: "lake -d docbuild build ComplexityTheory:docs",
				},
				{ name: "Build guide", run: "python -m mkdocs build --strict -f mkdocs.yml" },
				{
					name: "Assemble site",
					run: "cp -R docbuild/.lake/build/doc site/api",
				},
				{ name: "Upload Pages artifact", uses: uploadPages, with: { path: "site" } },
			],
		}),
		deploy: job({
			name: "Deploy documentation",
			needs: "build",
			if: "github.event_name == 'push' && github.ref == 'refs/heads/main'",
			"runs-on": "ubuntu-24.04",
			permissions: { pages: "write", "id-token": "write" },
			environment: {
				name: "github-pages",
				url: "${{ steps.deployment.outputs.page_url }}",
			},
			steps: [{ id: "deployment", name: "Deploy to GitHub Pages", uses: deployPages }],
		}),
	},
});
