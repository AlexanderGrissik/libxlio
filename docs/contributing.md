# Contributing to libvma-pro

As a contributor, here are the guidelines we would like you to follow:

 - [Submission Guidelines](#submit)
 - [Commit Message Guidelines](#commit)
 - [Coding Rules](#rules)
 - [Unit tests](#tests)


## <a name="submit"></a> Submission Guidelines


### Submitting an Issue

Before you submit an issue, please search the issue list, to understand if an issue for your problem already exists.


Please describe configuration details where issue is appeared.

A minimal reproduction step by step instruction allows us to quickly confirm a bug.


### Submitting a Pull Request

Before you submit your Pull Request (PR) consider the following guidelines:

1. Fork the `mellanox-lab/libvma-pro` repo.
2. Make your changes in a new git branch:
     ```shell
     git checkout -b fix-branch master
     ```
3. Do relevant modifications and include appropriate unit-test cases.
4. Follow our [Coding Rules](#rules).
5. Run the existing test suite as described in the [Test suite](#tests), and ensure that all tests pass.
6. Prepare sequence of small commits that as one self-contained change. Read [Why Write Small Commit](#patch).
7. Commit your changes using a descriptive commit message that follows our [Commit Message Conventions](#commit).
     ```shell
     git commit -a -s
     ```
8. Push your branch to GitHub:
    ```shell
    git push origin fix-branch
    ```
9. Select `vNext` as a base for pull request.
10. Address review feedback as described at [Reviewing a Pull Request](#review).
11. Ask verification after passing continuous integration and getting review approval.
12. Rebase your pull request on top of `vNext`.
13. Pull request is moved to `vNext` by authority person.
14. Update pull request in case regression report any issues related one.

### Reviewing a Pull Request

In doing a code review, you should make sure that:

* The code is well-designed.
* The functionality is good for the users of the code.
* Any parallel programming is done safely.
* The code isn’t more complex than it needs to be.
* The developer isn’t implementing things they might need in the future but don’t know they need now.
* Code has appropriate unit tests.
* Tests are well-designed.
* The developer used clear names for everything.
* Comments are clear and useful, and mostly explain why instead of what.
* Code is appropriately documented.
* The code conforms to our style guides.

Refer to good practices article from [Google](https://google.github.io/eng-practices/review/reviewer/standard.html).


### <a name="patch"></a> Why Write Small Commit?

* Reviewed more quickly. It’s easier for a reviewer to find five minutes several times to review small patches than to set aside a 30 minute block to review one large patch.
* Reviewed more thoroughly. With large changes, reviewers and authors tend to get frustrated by large volumes of detailed commentary shifting back and forth—sometimes to the point where important points get missed or dropped.
* Less likely to introduce bugs. Since you’re making fewer changes, it’s easier for you and your reviewer to reason effectively about the impact of the patch and see if a bug has been introduced.
* Less wasted work if they are rejected. If you write a huge patch and then your reviewer says that the overall direction is wrong, you’ve wasted a lot of work.
* Easier to merge. Working on a large patch takes a long time, so you will have lots of conflicts when you merge, and you will have to merge frequently.
* Easier to design well. It’s a lot easier to polish the design and code health of a small change than it is to refine all the details of a large change.
* Less blocking on reviews. Sending self-contained portions of your overall change allows you to continue coding while you wait for your current patch in review.
* Simpler to roll back. A large patch will more likely touch files that get updated between the initial patch submission and a rollback patch, complicating the rollback (the intermediate patches will probably need to be rolled back too).

Refer to good practices article from [Google](https://google.github.io/eng-practices/review/developer/small-cls.html).

### <a name="commit"></a> Commit Message Format

There are following rules for commit message format.

Each commit message consists of a **header**, a **body**, and a **footer** separated by blank line.

The `header` is mandatory and must conform to the [Commit Message Header](#commit-header) format.

The `body` is mandatory for fixes and features and must conform to the [Commit Message Body](#commit-body) format.

The `footer` is optional. See [Commit Message Footer](#commit-footer) format.

Any line of the commit message cannot be longer than 100 characters.


#### <a name="commit-header"></a>Commit Message Header

```
issue: <number> <short summary>
```

#### <a name="commit-body"></a>Commit Message Body

Message body must explain the motivation for the change. This commit message should explain **WHY** you are making the change.


#### <a name="commit-footer"></a>Commit Message Footer

The footer can contain information about contributors and reviewers.

`Signed-off-by: name <email>` certifies that you wrote it or otherwise have the right to pass it on as a open-source patch.

`Reviewed-by: name <email>` reviewer completely satisfied that the patch is ready for application.


## <a name="rules"></a> Coding Rules
Keep these rules in mind as you are working:

* All features or bug fixes **must be tested** by unit-tests.
* All public API methods **must be documented**.
* Code should follow [coding style guide](./coding-style.md).


## <a name="tests"></a> Unit tests
This set of tests is based on [Google Test C++] (https://github.com/google/googletest) environment 

Suite support [TAP protocol](https://en.wikipedia.org/wiki/Test_Anything_Protocol) for test result output.
Just set **GTEST_TAP=2** as  environment variable.

This suite includes standard socket api and library specific api tests.
**LD_PRELOAD** should be done to verify target library. 

Build standard tests:
```shell
$ make -C tests/gtest
```

Build specific tests:
```shell
$ make -C tests/gtest CPPFLAGS="-DVMA_EXTRA_API_ENABLED=1"
```

Display help:
```shell
$ ./tests/gtest --help
```

All tests can be launched on single node that has two interfaces.

Run tests:
```shell
$ ./tests/gtest --addr=1.1.3.6:1.1.4.6
```
or
```shell
$ ./tests/gtest --if=ens2f0:ens2f1 --gtest_filter=tcp_sendfile.*
```
