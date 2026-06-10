# Raw research extracts — Merge Queues & Required Checks

Topic: GitHub merge queue mechanics, required-check selection, branch protection vs rulesets, batching trade-offs. Fetched via scrapling (`Fetcher.get`, stealthy headers). All retrievals 2026-06-10.

Dropped source: Uber's own blog post "Keeping master green at scale" — both `https://www.uber.com/blog/research/keeping-master-green-at-scale/` and `https://eng.uber.com/research/keeping-master-green-at-scale/` returned 404 on 2026-06-10. Substituted Adrian Colyer's *the morning paper* summary of the underlying EuroSys'19 paper (source 5 below).

---

## Source 1 — GitHub Docs: Managing a merge queue

- URL: https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue
- Retrieved: 2026-06-10 (HTTP 200)

Extracted passages:

> A merge queue helps increase velocity by automating pull request merges into a busy branch and ensuring the branch is never broken by incompatible changes. The merge queue provides the same benefits as the Require branches to be up to date before merging branch protection, but does not require a pull request author to update their pull request branch and wait for status checks to finish before trying to merge. Using a merge queue is particularly useful on branches that have a relatively high number of pull requests merging each day from many different users.

> Once a pull request has passed all required branch protection checks, a user with write access to the repository can add the pull request to the queue. The merge queue will ensure the pull request's changes pass all required status checks when applied to the latest version of the target branch and any pull requests already in the queue.

> Note: A merge queue cannot be enabled with branch protection rules that use wildcard characters (*) in the branch name pattern.

> A merge queue will wait for required checks to be reported before it can proceed with merging. You must update your CI configuration to trigger and report on merge group events when requiring a merge queue. Merge queue and pull requests checks are coupled and configured under branch protection rules or rulesets.

> You must use the `merge_group` event to trigger your GitHub Actions workflow when a pull request is added to a merge queue. ... If your repository uses GitHub Actions to perform required checks on pull requests in your repository, you need to update the workflows to include the `merge_group` event as an additional trigger. Otherwise, status checks will not be triggered when you add a pull request to a merge queue. The merge will fail as the required status check will not be reported. The `merge_group` event is separate from the `pull_request` and `push` events.

```yaml
on:
  pull_request:
  merge_group:
```

> With third-party CI providers, you will need to update your CI configuration to run when a branch that begins with the special prefix `gh-readonly-queue/{base_branch}` is pushed to. These are the temporary branches that are created on your behalf by a merge queue and contain a different sha from the pull request.

> Repository administrators can require a merge queue by enabling the branch protection setting "Require merge queue" in the protection rules for the base branch.

Settings exposed once "Require merge queue" is on:

> **Merge method:** Select which method to use when merging queued pull requests: merge, rebase, or squash.
> **Build concurrency:** The maximum number of `merge_group` webhooks to dispatch (between 1 and 100), throttling the total amount of concurrent CI builds. This affects the velocity of merges that a merge queue can complete.
> **Only merge non-failing pull requests:** This setting determines how a merge queue forms groups of pull requests to be merged. [Yes:] All pull requests must satisfy required checks to be merged. [No:] Pull requests that have failed required checks can be added to a group as long as the last pull request in the group has passed required checks. ... Leaving this checkbox unselected can be useful if you have intermittent test failures, but don't want false negatives to hold up the queue.
> **Status check timeout:** Choose how long the queue should wait for a response from CI before assuming that checks have failed.
> **Merge limits:** Select the minimum and maximum number of pull requests to merge into the base branch at the same time (between 1 and 100), and a timeout after which the queue should stop waiting for more entries and merge with fewer than the minimum number. ... Merge limits do not combine `merge_group` builds. Merge limits only affect merges to the base branch once one or more `merge_group` has satisfied build checks.

> Maximum pull requests to merge: You can specify a maximum group size, which is useful if merges to your base branch trigger a deployment, and you want to make sure you're not deploying too many changes at once. Minimum pull requests to merge: You can specify a minimum group size, which is useful if merges to your base branch trigger a lengthy CI build or deploy process, and you don't want to hold up the following entries in the queue. Wait time: You can specify a timeout for reaching the minimum group size.

> As pull requests are added to the merge queue, the merge queue ensures that they are merged in a first-in-first-out order where the required checks are always satisfied. A merge queue creates temporary branches with a special prefix to validate pull request changes. When a pull request is added to the merge queue, the changes in the pull request are grouped into a `merge_group` with the latest version of the `base_branch` as well as changes from pull requests ahead of it in the queue.

> After grouping a pull request with the latest version of the target branch and changes ahead of it in the queue, if there are failed required status checks or conflicts with the base branch, the pull request will be removed from the queue. ... The merge queue recreates the temporary branch [for the entries behind it] to only contain changes from the target branch and [the surviving] pull request.

Removal reasons:

> Configured CI service is reporting test failures for a merge group; Timed out awaiting a successful CI result based off the configured timeout setting; User requesting a removal via the API or merge queue interface; Branch protection failure that could not automatically be resolved.

> Be aware that jumping to the top of a merge queue will cause a full rebuild of all in-progress pull requests, as the reordering of the queue introduces a break in the commit graph. Heavily utilizing this feature can slow down the velocity of merges for your target branch.

---

## Source 2 — GitHub Engineering Blog: How GitHub uses merge queue to ship hundreds of changes every day

- URL: https://github.blog/engineering/engineering-principles/how-github-uses-merge-queue-to-ship-hundreds-of-changes-every-day/
- Authors: Will Smythe & Lawrence Gripper, 2024-03-06
- Retrieved: 2026-06-10 (HTTP 200)

Extracted passages:

> By 2016, nearly 1,000 pull requests were merging into our large monorepo every month. ... Our solution at this time was trains. A train was a special pull request that grouped together multiple pull requests (passengers) that would be tested, deployed, and eventually merged at the same time. A user (called a conductor) was responsible for handling most aspects of the process.

> Trains helped improve velocity at first, but over time started to negatively impact developer satisfaction and increase the time to land a pull request. ... Trains could also grow large, containing the changes of 15 pull requests. Large trains frequently "derailed" due to a deployment issue, conflicts, or the need for an engineer to remove their change. On painful occasions, developers could wait 8+ hours after joining a train for it to ship, only for it to be removed due to a conflict between two pull requests in the train.

Design goals for the replacement:

> Improve the developer experience of shipping. Engineers wanted to express two simple intents: "I want to ship this change" and "I want to shift to other work;" the system should handle the rest.
> Avoid having problematic pull requests impact everyone. Those causing conflicts or build failures should not impact all other pull requests waiting to merge. The throughput of the overall system should be favored over fairness to an individual pull request.
> Be consistent and as automated as possible across our services and repositories. Manual toil by engineers should be removed wherever possible.

> Merge queue has become the single entry point for shipping code changes at GitHub. It was designed and tested at scale, shipping 30,000+ pull requests with their associated 4.5 million CI runs, for GitHub.com before merge queue was made generally available.

> For GitHub and our "deploy the merge process," merge queue dynamically forms groups of pull requests that are candidates for deployment, kicks off builds and tests via GitHub Actions, and ensures our main branch is never updated to a failing commit by enforcing branch protection rules. Pull requests in the queue that conflict with one another are automatically detected and removed, with the queue automatically re-forming groups as needed.

> Trains (our old system) previously limited our ability to deploy more than 15 changes at once, but now we can now safely deploy 30 or more if needed. Every month, over 500 engineers merge 2,500 pull requests into our large monorepo with merge queue, more than double the volume from a few years ago. The average wait time to ship a change has also been reduced by 33%.

---

## Source 3 — GitHub Docs: About rulesets

- URL: https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/about-rulesets
- Retrieved: 2026-06-10 (HTTP 200)

Extracted passages:

> A ruleset is a named list of rules that applies to a repository or to multiple repositories in an organization for customers on GitHub Team and GitHub Enterprise plans. You can have up to 75 rulesets per repository.

> When you create a ruleset, you can allow certain users to bypass the rules in the ruleset. This can be users with a certain role, such as repository administrator, or it can be specific teams or GitHub Apps.

> You can use fnmatch syntax to define a pattern to target specific branches and tags. For example, you could use the pattern `releases/**/*` to target all branches in your repository whose name starts with the string `releases/`.

> Rulesets work alongside any branch protection rules in a repository. Many of the rules you can define in rulesets are similar to protection rules, and you can start using rulesets without overriding any of your existing protection rules.

Advantages over branch protection rules:

> Unlike protection rules, multiple rulesets can apply at the same time, so you can be confident that every rule targeting a branch in your repository will be evaluated when someone interacts with that branch.
> Rulesets have statuses, so you can easily manage which rulesets are active in a repository without needing to delete rulesets.
> Anyone with read access to a repository can view the active rulesets for the repository. This means a developer can understand why they have hit a rule, or an auditor can check the security constraints for the repository, without requiring admin access to the repository.
> You can create additional rules to control the metadata of commits entering a repository, such as the commit message and the author's email address [Enterprise].

> A ruleset does not have a priority. Instead, if multiple rulesets target the same branch or tag in a repository, the rules in each of these rulesets are aggregated. If the same rule is defined in different ways across the aggregated rulesets, the most restrictive version of the rule applies. As well as layering with each other, rulesets also layer with protection rules targeting the same branch or tag.

> [Layering example:] An administrator of the repository has set up a ruleset targeting the my-feature branch. This ruleset requires signed commits, and three reviews on pull requests before they can be merged. An existing branch protection rule for the my-feature branch requires a linear commit history, and two reviews. ... The result is that the most restrictive version of the rule applies: the my-feature branch requires signed commits and a linear commit history, and pull requests targeting the branch will require three reviews.

> Enforcement statuses: Active — your ruleset will be enforced upon creation. Disabled — your ruleset will not be enforced.

---

## Source 4 — Shopify Engineering: Successfully Merging the Work of 1000+ Developers

- URL: https://shopify.engineering/successfully-merging-work-1000-developers
- Author: Jack Li, 2019-11-14
- Retrieved: 2026-06-10 (HTTP 200)

Extracted passages:

> Shopify changes 40 times a day. We follow a trunk-based development workflow and merge around 400 commits to master daily.

Three rules:

> Master must always be green (passing CI). Important because we must be able to deploy from master at all times. If master is not green, our developers cannot merge, slowing all development across Shopify.
> Master must stay close to production. Drifting master too far ahead of what is deployed to production increases risk.
> Emergency merges must be fast. In case of emergencies, we must be able to quickly merge fixes intended to resolve the incident.

> [v1 problem:] Merge Queue v1 kept track of pull requests, but we were not running CI on pull requests while they sat in the queue. ... There was also no guarantee that a pull request in the queue would pass CI after it was merged, since there could be soft conflicts (two pull requests that pass CI independently, but fail when merged together) between pull requests in the queue.

> Jumping the queue by merging directly to master is bad for overall throughput. To ensure that everyone uses the queue, we disable the ability to merge directly to master using GitHub branch protection programmatically as part of the merge queue onboarding process. However, we still need to be able to bypass the queue in an emergency ... we added a separate `/shipit --emergency` command that skips any checks and merges directly to master. This helps communicate to developers that this action is reserved for emergencies only and gives us auditability into the cases where this gets used.

> If we run CI before merging to master, we ensure that only green changes merge. This improves the local development experience by eliminating the cases of pulling a broken master, and by speeding up the deploy process by not having to worry about delays due to a failing build. Our solution here is to have what we call a "predictive branch," implemented as a git branch, onto which pull requests are merged, and CI is run.

Flaky-test tolerance:

> The existence of these flaky tests makes removing pull requests from the queue difficult because we lack certainty about whether failed tests are legitimate or flaky. ... We added a failure-tolerance threshold, and only remove pull requests when the number of successive failures exceeds the failure tolerance. This is based on the idea that legitimate failures will propagate to all later CI runs, but flaky tests will not block later CI runs from passing. Larger failure tolerances will increase the accuracy, but at the tradeoff of taking longer to remove problematic changes from the queue.

> [With an assumed 25% flakiness rate, false-positive probability by failure tolerance:] 0 → 25%; 1 → 6.25%; 2 → 1.5%; 3 → 0.39%; 4 → 0.097%. ... a value of 3 will bring us sufficiently close. This means that on the fourth consecutive failure, we will remove the first pull request failing CI from the queue.

Batching:

> To optimize the number of pull requests for each deploy, we split the pull requests in the merge queue up into batches. We define a batch as the maximum number of pull requests we can put in a single deploy. Larger batches result in higher theoretical throughput, but higher risk. In practice, the increased risk of larger batches impedes throughput by causing failures that are harder to isolate, and results in an increased number of rollbacks. In our application, we went with a batch size of 8 as a balance between throughput and risk.

> At any given time, we run CI on 3 batches worth of pull requests in the queue. Having a bounded number of batches ensures that we're only using CI resources on what we will need soon, rather than the entire set of pull requests in the queue. This helps reduce cost and resource utilization.

---

## Source 5 — the morning paper (Adrian Colyer): Keeping master green at scale (Uber SubmitQueue, EuroSys'19)

- URL: https://blog.acolyer.org/2019/04/18/keeping-master-green-at-scale/
- Summarizes: Ananthanarayanan et al., "Keeping master green at scale", EuroSys 2019 (Uber). Uber's own blog page for the paper is dead (404), see header note.
- Retrieved: 2026-06-10 (HTTP 200)

Extracted passages:

> A mainline is called green if all build steps (e.g., compilation, unit tests, UI tests) can successfully execute for every commit point in the history. Keeping the mainline green allows developers to (i) instantly release new features from any commit point in the mainline, (ii) roll back to any previously committed change, and not necessarily to the last working version, and (iii) always develop against the most recent and healthy version of the monorepo.

> [9 months of data for the Uber iOS and Android repos:] At 'only' 16 concurrent and potentially conflicting changes, there's a 40% chance of a problem. ... despite all efforts to minimize mainline breakages, it is very likely that the mainline experiences daily breakages due to the sheer volume of everyday code changes committed to a big monorepo. ... Here's a one week view of the iOS mainline prior to the introduction of SubmitQueue. The mainline was green only 52% of the time. (Since the introduction of SubmitQueue over a year ago, mainlines have remained green at all times).

> The simplest solution to keep the mainline green is to enqueue every change that gets submitted to the system. A change at the head of the queue gets committed into the mainline if its build steps succeed. For instance, the rust project uses this technique to ensure that the mainline remains healthy all the time. This approach does not scale as the number of changes grows. For instance, with a thousand changes per day, where each change takes 30 minutes to pass all build steps, the turnaround time of the last enqueued change will be over 20 days.

> One possible solution to reduce the latency is batching changes, but then we're back at the problem of conflicts and complex manual resolution if we're not careful. Another tactic is optimistic execution ... This approach suffers from high failure rates and turnaround times still though as failure of a change can abort many optimistically executing builds.

> SubmitQueue guarantees an always green mainline by providing the illusion of a single queue where every change gets enqueued, performs all its build steps, and ultimately gets merged with the mainline branch if all build steps succeed. ... In order to scale to thousands of changes per day while ensuring serializability, the planner engine speculates on outcomes of pending changes using a speculation engine, and executes their corresponding builds in parallel by using a build controller.

> Roughly speaking, two changes conflict if they both affect a common set of build targets. Every build target is associated with a unique target hash that represents its current state.

> We trained our success prediction models in a supervised manner using logistic regression. ... The trained model achieved 97% accuracy. The features with the highest positive correlation scores were: the number of successful speculations so far; revision and revert test plans included as part of the submission; the number of initial tests that succeeded before submitting a change.

> The current version of SubmitQueue respects the order in which changes are submitted to the system. Thus small changes can be backed up behind larger ones. Future work will include re-ordering of non-independent changes to improve throughput. Another optimisation to be explored is batching independent changes expected to succeed together.

---

## Source 6 — Graydon Hoare: "not rocket science" (the story of monotone and bors)

- URL: https://graydon2.dreamwidth.org/1597.html
- Author: Graydon Hoare (Rust's original designer), 2014-02-02
- Retrieved: 2026-06-10 (HTTP 200)

Extracted passages:

> The Not Rocket Science Rule Of Software Engineering: automatically maintain a repository of code that always passes all the tests.

> The system had a simple job: automatically maintain a repository of code that always passes all the tests. It gave us peace of mind (customers only pulled from that repository, so never saw breakage) and had the important secondary benefit that engineers could do their day's work from known-good revisions, without hunting someone else's bug that accidentally slipped in. Because the system was automated, we knew there was no chance anyone would rush to commit something sloppy.

> That is, everywhere I saw "continuous integration" in practice, it was being done in the wrong order: code being accepted before testing (leaving a potentially broken tree), or tested in isolation and then integrated on the basis of that test (with no guarantee that the integrated combination works). Continuous integration seemed everywhere to be used only to learn (rapidly) when the tree was broken, not prevent it breaking in the first place.

> Bors implements the Not Rocket Science Rule against a combination of a buildbot test farm and a github repository: it monitors pull requests, waits for reviewers to approve them, then for each approved revision, makes a temporary integration revision which extends your integration branch by the proposed changes. It tests that temporary revision and advances your integration branch to point to the integration revision if and only if the tests pass. If the tests fail, the integration revision is discarded and a comment in the pull request is left showing the failures.

> Trunk is never broken. It does mean that your integration cycle time is bounded by your test cycle time, and it means that some changes take a number of attempts to integrate (bors supports priority markers to help you manually tune the integration order).

> On some projects, test time is too long for this strategy to work on each revision, at least without defining an integration-test subset. This is certainly everyone's chief initial concern, and it's legitimate, but in my experience it's a bit like people objecting to testing (or typechecking) in the first place because writing the tests and types will take too long: you'll spend much more time fighting the bugs if you wait and discover them later.

> [From a comment by the author, on Travis-style PR testing:] it tells you whether the PR passed when merged into master, at the time when the test was run. But if other PRs have been merged since then, then the result may be stale.
